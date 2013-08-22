package org.sireum.analyseLibrary.framework.amandroid

/*
 * Fengguo Wei, Kansas State University. Implement this library analyse framework.
 * @author <a href="mailto:fgwei@k-state.edu">Fengguo Wei</a>                           
*/

import org.sireum.test.framework._
import org.sireum.pilar.ast._
import org.sireum.pilar.parser._
import org.sireum.util._
import org.sireum.pipeline._
import org.sireum.core.module.AlirIntraProceduralModule
import java.io.PrintWriter
import java.util.zip.ZipFile
import org.sireum.core.module.ChunkingPilarParserModule
import org.sireum.pilar.symbol.SymbolTable
import org.sireum.pilar.symbol.ProcedureSymbolTable
import org.sireum.pilar.symbol.ProcedureSymbolTableData
import org.sireum.alir.ControlFlowGraph
import java.util.zip.GZIPInputStream
import java.io.File
import org.sireum.amandroid.symbolResolver.AndroidLibInfoTables
import org.sireum.amandroid.android.cache.AndroidCacheFile
import org.sireum.amandroid.module._

trait PreprocessLibraryFrameWork extends TestFramework { 
  
  //////////////////////////////////////////////////////////////////////////////
  // Implemented Public Methods
  //////////////////////////////////////////////////////////////////////////////

  def Analyzing : this.type = this

  def title(s : String) : this.type = {
    _title = caseString + s
    this
  }

  def file(fileUri : FileResourceUri, alit : AndroidLibInfoTables, aCache : AndroidCacheFile[ResourceUri]) =
    AmandroidConfiguration(title, fileUri, alit, aCache)

  //////////////////////////////////////////////////////////////////////////////
  // Public Case Classes
  //////////////////////////////////////////////////////////////////////////////

  case class AmandroidConfiguration //
  (title : String, srcs : FileResourceUri, alit : AndroidLibInfoTables, aCache : AndroidCacheFile[ResourceUri]) {

    ////////////////////////////////////////////////////////////////////////////
    // Test Constructor
    ////////////////////////////////////////////////////////////////////////////

    test(title) {
      println("####" + title + "#####")
        val f = new File(srcs.toString().substring(5))
        //create directory
        val nameArray = f.getName().split("\\.")
        var dirName : String = ""
        for(i <- 0 until nameArray.length-1){
          dirName += nameArray(i)
        }
        val d = srcs.substring(srcs.indexOf("/"), srcs.lastIndexOf("/")+1)
        val srcFiles = mlistEmpty[FileResourceUri]
        /*for start analysis from pilar file*/
        val resDir = new File(d+"../result")
        if(!resDir.exists()){
          resDir.mkdir()
        }

        /*end here*/
        val job = PipelineJob()
        val options = job.properties

        ChunkingPilarParserModule.setSources(options, ilist(Right(FileUtil.toUri(d+ "/" +f.getName()))))
        PilarAndroidSymbolResolverModule.setHasExistingAndroidLibInfoTables(options, Some(alit))
        PilarAndroidSymbolResolverModule.setShouldBuildLibInfoTables(options, false)
        AndroidIntraProceduralModule.setAndroidLibInfoTablesOpt(options, Some(alit))
        AndroidIntraProceduralModule.setParallel(options, true)
        AndroidIntraProceduralModule.setAndroidCache(options, Some(aCache))
        AndroidIntraProceduralModule.setShouldBuildCfg(options, true)
        AndroidIntraProceduralModule.setShouldBuildRda(options, true)
        AndroidIntraProceduralModule.setShouldBuildPag(options, true)
        pipeline.compute(job)

        if (job.lastStageInfo.hasError) {
	        val pwOut = new PrintWriter(Console.out)
	        val pwErr = new PrintWriter(Console.err)
	        println("Errors from stage: " + job.lastStageInfo.title)
	        val stageTags = job.lastStageInfo.tags.toList
	        PipelineUtil.printTags(stageTags, pwOut, pwErr)
	        pwErr.println(Tag.collateAsString(job.lastStageInfo.tags.toList))
	        pwErr.flush
	        for (m <- job.lastStageInfo.info) {
	          val mTags = m.tags.toList
	          PipelineUtil.printTags(mTags, pwOut, pwErr)
	          pwErr.println(Tag.collateAsString(mTags))
	          pwErr.flush
	        }
	      }
        
        println("pipeline done!")
        
        println("start convert cfg, pag to xml!")
        val intraResult = AndroidIntraProceduralModule.getIntraResult(options)
        intraResult.keys.foreach(
          key =>
          {
            aCache.save[AndroidIntraProcedural.CFG](key, "cfg", intraResult(key).cfg)
            intraResult(key).pagOpt match {
              case Some(pag) =>
                aCache.save(key, "pag", pag)
              case None =>
            }
          }  
        )
        
        println("###############################################")
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // Implemented Protected Methods and Fields
  //////////////////////////////////////////////////////////////////////////////

  protected var _title : String = null
  protected var num = 0
  protected def title() = if (_title == null) {
    num += 1
    "Analysis #" + num
  } else _title

  protected val pipeline =
    PipelineConfiguration(
      "Library analyse pipeline",
      false,
      PipelineStage(
        "Chunking pilar parsing stage",
        false,
        ChunkingPilarParserModule
      ),
      PipelineStage(
        "PilarAndroidSymbolResolverModule stage",
        false,
        PilarAndroidSymbolResolverModule
      )
      ,
      PipelineStage(
        "Android IntraProcedural Analysis",
        false,
        AndroidIntraProceduralModule
      )
    )
    
}